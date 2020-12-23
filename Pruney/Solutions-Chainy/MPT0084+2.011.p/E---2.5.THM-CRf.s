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
% DateTime   : Thu Dec  3 10:33:23 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.09s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 148 expanded)
%              Number of clauses        :   33 (  67 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 237 expanded)
%              Number of equality atoms :   13 (  87 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(t27_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r1_xboole_0(X1,X2)
          & r1_tarski(X1,X3)
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t77_xboole_1])).

fof(c_0_10,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k3_xboole_0(X19,X20) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_11,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_13,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    & r1_tarski(esk2_0,esk4_0)
    & r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X15,X16,X17,X18] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(k3_xboole_0(X15,X17),k3_xboole_0(X16,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_xboole_1])])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_16]),c_0_16])).

fof(c_0_23,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_16])).

fof(c_0_25,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_xboole_0(X26,X27)
      | r1_xboole_0(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_16])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_30])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_40,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X2,X4)
    | ~ r1_tarski(X1,X5)
    | ~ r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_37])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk2_0)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 6.09/6.25  # AutoSched0-Mode selected heuristic G_____X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN
% 6.09/6.25  # and selection function SelectComplexExceptUniqMaxHorn.
% 6.09/6.25  #
% 6.09/6.25  # Preprocessing time       : 0.027 s
% 6.09/6.25  # Presaturation interreduction done
% 6.09/6.25  
% 6.09/6.25  # Proof found!
% 6.09/6.25  # SZS status Theorem
% 6.09/6.25  # SZS output start CNFRefutation
% 6.09/6.25  fof(t77_xboole_1, conjecture, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 6.09/6.25  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.09/6.25  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.09/6.25  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.09/6.25  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.09/6.25  fof(t27_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 6.09/6.25  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.09/6.25  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 6.09/6.25  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.09/6.25  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t77_xboole_1])).
% 6.09/6.25  fof(c_0_10, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k3_xboole_0(X19,X20)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 6.09/6.25  fof(c_0_11, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 6.09/6.25  fof(c_0_12, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 6.09/6.25  fof(c_0_13, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 6.09/6.25  fof(c_0_14, negated_conjecture, ((~r1_xboole_0(esk2_0,esk3_0)&r1_tarski(esk2_0,esk4_0))&r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 6.09/6.25  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 6.09/6.25  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 6.09/6.25  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 6.09/6.25  cnf(c_0_18, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.09/6.25  fof(c_0_19, plain, ![X15, X16, X17, X18]:(~r1_tarski(X15,X16)|~r1_tarski(X17,X18)|r1_tarski(k3_xboole_0(X15,X17),k3_xboole_0(X16,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_xboole_1])])).
% 6.09/6.25  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.09/6.25  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 6.09/6.25  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_16]), c_0_16])).
% 6.09/6.25  fof(c_0_23, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 6.09/6.25  cnf(c_0_24, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_18, c_0_16])).
% 6.09/6.25  fof(c_0_25, plain, ![X25, X26, X27]:(~r1_tarski(X25,X26)|~r1_xboole_0(X26,X27)|r1_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 6.09/6.25  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.09/6.25  fof(c_0_27, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 6.09/6.25  cnf(c_0_28, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_20, c_0_16])).
% 6.09/6.25  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 6.09/6.25  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.09/6.25  cnf(c_0_31, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 6.09/6.25  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 6.09/6.25  cnf(c_0_33, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.09/6.25  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_16])).
% 6.09/6.25  cnf(c_0_35, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.09/6.25  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_28, c_0_22])).
% 6.09/6.25  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_22]), c_0_30])])).
% 6.09/6.25  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 6.09/6.25  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_32, c_0_16])).
% 6.09/6.25  cnf(c_0_40, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_tarski(X2,X4)|~r1_tarski(X1,X5)|~r1_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 6.09/6.25  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 6.09/6.25  cnf(c_0_42, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_37])).
% 6.09/6.25  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 6.09/6.25  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk2_0)|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 6.09/6.25  cnf(c_0_45, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.09/6.25  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 6.09/6.25  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 6.09/6.25  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_46, c_0_22])).
% 6.09/6.25  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_47, c_0_30])).
% 6.09/6.25  cnf(c_0_50, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 6.09/6.25  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), ['proof']).
% 6.09/6.25  # SZS output end CNFRefutation
% 6.09/6.25  # Proof object total steps             : 52
% 6.09/6.25  # Proof object clause steps            : 33
% 6.09/6.25  # Proof object formula steps           : 19
% 6.09/6.25  # Proof object conjectures             : 13
% 6.09/6.25  # Proof object clause conjectures      : 10
% 6.09/6.25  # Proof object formula conjectures     : 3
% 6.09/6.25  # Proof object initial clauses used    : 12
% 6.09/6.25  # Proof object initial formulas used   : 9
% 6.09/6.25  # Proof object generating inferences   : 14
% 6.09/6.25  # Proof object simplifying inferences  : 15
% 6.09/6.25  # Training examples: 0 positive, 0 negative
% 6.09/6.25  # Parsed axioms                        : 9
% 6.09/6.25  # Removed by relevancy pruning/SinE    : 0
% 6.09/6.25  # Initial clauses                      : 12
% 6.09/6.25  # Removed in clause preprocessing      : 1
% 6.09/6.25  # Initial clauses in saturation        : 11
% 6.09/6.25  # Processed clauses                    : 79515
% 6.09/6.25  # ...of these trivial                  : 278
% 6.09/6.25  # ...subsumed                          : 75877
% 6.09/6.25  # ...remaining for further processing  : 3360
% 6.09/6.25  # Other redundant clauses eliminated   : 0
% 6.09/6.25  # Clauses deleted for lack of memory   : 0
% 6.09/6.25  # Backward-subsumed                    : 588
% 6.09/6.25  # Backward-rewritten                   : 202
% 6.09/6.25  # Generated clauses                    : 830614
% 6.09/6.25  # ...of the previous two non-trivial   : 774287
% 6.09/6.25  # Contextual simplify-reflections      : 25
% 6.09/6.25  # Paramodulations                      : 830614
% 6.09/6.25  # Factorizations                       : 0
% 6.09/6.25  # Equation resolutions                 : 0
% 6.09/6.25  # Propositional unsat checks           : 0
% 6.09/6.25  #    Propositional check models        : 0
% 6.09/6.25  #    Propositional check unsatisfiable : 0
% 6.09/6.25  #    Propositional clauses             : 0
% 6.09/6.25  #    Propositional clauses after purity: 0
% 6.09/6.25  #    Propositional unsat core size     : 0
% 6.09/6.25  #    Propositional preprocessing time  : 0.000
% 6.09/6.25  #    Propositional encoding time       : 0.000
% 6.09/6.25  #    Propositional solver time         : 0.000
% 6.09/6.25  #    Success case prop preproc time    : 0.000
% 6.09/6.25  #    Success case prop encoding time   : 0.000
% 6.09/6.25  #    Success case prop solver time     : 0.000
% 6.09/6.25  # Current number of processed clauses  : 2559
% 6.09/6.25  #    Positive orientable unit clauses  : 60
% 6.09/6.25  #    Positive unorientable unit clauses: 2
% 6.09/6.25  #    Negative unit clauses             : 3
% 6.09/6.25  #    Non-unit-clauses                  : 2494
% 6.09/6.25  # Current number of unprocessed clauses: 690098
% 6.09/6.25  # ...number of literals in the above   : 2791427
% 6.09/6.25  # Current number of archived formulas  : 0
% 6.09/6.25  # Current number of archived clauses   : 802
% 6.09/6.25  # Clause-clause subsumption calls (NU) : 3463107
% 6.09/6.25  # Rec. Clause-clause subsumption calls : 2669200
% 6.09/6.25  # Non-unit clause-clause subsumptions  : 76117
% 6.09/6.25  # Unit Clause-clause subsumption calls : 214
% 6.09/6.25  # Rewrite failures with RHS unbound    : 0
% 6.09/6.25  # BW rewrite match attempts            : 212
% 6.09/6.25  # BW rewrite match successes           : 16
% 6.09/6.25  # Condensation attempts                : 0
% 6.09/6.25  # Condensation successes               : 0
% 6.09/6.25  # Termbank termtop insertions          : 14932119
% 6.09/6.28  
% 6.09/6.28  # -------------------------------------------------
% 6.09/6.28  # User time                : 5.703 s
% 6.09/6.28  # System time              : 0.237 s
% 6.09/6.28  # Total time               : 5.939 s
% 6.09/6.28  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:37 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 146 expanded)
%              Number of clauses        :   32 (  68 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :   73 ( 205 expanded)
%              Number of equality atoms :   15 (  75 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t80_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t77_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
       => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    inference(assume_negation,[status(cth)],[t81_xboole_1])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_11,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_xboole_0(X28,X29)
      | r1_xboole_0(X28,k4_xboole_0(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X16,X17,X18] : k3_xboole_0(X16,k4_xboole_0(X17,X18)) = k4_xboole_0(k3_xboole_0(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_16,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( r1_xboole_0(X23,X24)
      | ~ r1_tarski(X23,X25)
      | ~ r1_xboole_0(X23,k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_27]),c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X2,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,X1),esk2_0)
    | ~ r1_tarski(k4_xboole_0(esk1_0,X1),k4_xboole_0(X2,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)),k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_39])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_40])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X3,X4),X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_24]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(X2,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,esk3_0))
    | ~ r1_tarski(k4_xboole_0(esk2_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)
    | ~ r1_tarski(k4_xboole_0(esk1_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.20/0.39  # and selection function SelectNewComplexAHP.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t81_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.20/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.39  fof(t80_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 0.20/0.39  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.39  fof(t77_xboole_1, axiom, ![X1, X2, X3]:~(((~(r1_xboole_0(X1,X2))&r1_tarski(X1,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 0.20/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t81_xboole_1])).
% 0.20/0.39  fof(c_0_10, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.39  fof(c_0_12, plain, ![X28, X29, X30]:(~r1_xboole_0(X28,X29)|r1_xboole_0(X28,k4_xboole_0(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_xboole_1])])).
% 0.20/0.39  cnf(c_0_13, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_15, plain, ![X16, X17, X18]:k3_xboole_0(X16,k4_xboole_0(X17,X18))=k4_xboole_0(k3_xboole_0(X16,X17),X18), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.39  fof(c_0_16, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.39  cnf(c_0_17, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.39  cnf(c_0_19, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_21, plain, ![X11, X12, X13]:k4_xboole_0(k4_xboole_0(X11,X12),X13)=k4_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.39  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 0.20/0.39  cnf(c_0_24, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  fof(c_0_25, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.39  fof(c_0_26, plain, ![X23, X24, X25]:(r1_xboole_0(X23,X24)|~r1_tarski(X23,X25)|~r1_xboole_0(X23,k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_xboole_1])])])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_22])).
% 0.20/0.39  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.39  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_27]), c_0_24])).
% 0.20/0.39  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.39  fof(c_0_33, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.39  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_30, c_0_20])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,X1),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X2,esk3_0))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.39  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,X1),esk2_0)|~r1_tarski(k4_xboole_0(esk1_0,X1),k4_xboole_0(X2,esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.39  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_24])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X1)),k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_17, c_0_39])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_13, c_0_40])).
% 0.20/0.39  cnf(c_0_42, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X3,X4),X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_24]), c_0_32])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(X2,esk3_0))))), inference(spm,[status(thm)],[c_0_41, c_0_32])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,esk3_0))|~r1_tarski(k4_xboole_0(esk2_0,X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,X1),k4_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_36])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_13, c_0_45])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)|~r1_tarski(k4_xboole_0(esk1_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_36])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_48]), c_0_49]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 51
% 0.20/0.39  # Proof object clause steps            : 32
% 0.20/0.39  # Proof object formula steps           : 19
% 0.20/0.39  # Proof object conjectures             : 21
% 0.20/0.39  # Proof object clause conjectures      : 18
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 10
% 0.20/0.39  # Proof object initial formulas used   : 9
% 0.20/0.39  # Proof object generating inferences   : 19
% 0.20/0.39  # Proof object simplifying inferences  : 8
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 11
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 12
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 11
% 0.20/0.39  # Processed clauses                    : 243
% 0.20/0.39  # ...of these trivial                  : 103
% 0.20/0.39  # ...subsumed                          : 16
% 0.20/0.39  # ...remaining for further processing  : 124
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 3
% 0.20/0.39  # Generated clauses                    : 1552
% 0.20/0.39  # ...of the previous two non-trivial   : 1033
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 1552
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 110
% 0.20/0.39  #    Positive orientable unit clauses  : 87
% 0.20/0.39  #    Positive unorientable unit clauses: 1
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 20
% 0.20/0.39  # Current number of unprocessed clauses: 812
% 0.20/0.39  # ...number of literals in the above   : 974
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 15
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 154
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 148
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 14
% 0.20/0.39  # Unit Clause-clause subsumption calls : 3
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 175
% 0.20/0.39  # BW rewrite match successes           : 3
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 20647
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.044 s
% 0.20/0.39  # System time              : 0.009 s
% 0.20/0.39  # Total time               : 0.053 s
% 0.20/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------

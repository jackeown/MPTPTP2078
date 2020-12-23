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
% DateTime   : Thu Dec  3 10:33:39 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   33 (  86 expanded)
%              Number of clauses        :   20 (  38 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 ( 128 expanded)
%              Number of equality atoms :   21 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t81_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
       => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    inference(assume_negation,[status(cth)],[t81_xboole_1])).

fof(c_0_7,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_8,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk1_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk2_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_28]),c_0_18]),c_0_23]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_30]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.91/2.09  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 1.91/2.09  # and selection function SelectNewComplexAHP.
% 1.91/2.09  #
% 1.91/2.09  # Preprocessing time       : 0.037 s
% 1.91/2.09  # Presaturation interreduction done
% 1.91/2.09  
% 1.91/2.09  # Proof found!
% 1.91/2.09  # SZS status Theorem
% 1.91/2.09  # SZS output start CNFRefutation
% 1.91/2.09  fof(t81_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 1.91/2.09  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.91/2.09  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.91/2.09  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.91/2.09  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.91/2.09  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.91/2.09  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t81_xboole_1])).
% 1.91/2.09  fof(c_0_7, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 1.91/2.09  fof(c_0_8, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.91/2.09  fof(c_0_9, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.91/2.09  fof(c_0_10, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 1.91/2.09  cnf(c_0_11, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.91/2.09  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.91/2.09  fof(c_0_13, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.91/2.09  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.91/2.09  cnf(c_0_15, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.91/2.09  cnf(c_0_16, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.91/2.09  cnf(c_0_17, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 1.91/2.09  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.91/2.09  fof(c_0_19, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.91/2.09  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_12])).
% 1.91/2.09  cnf(c_0_21, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.91/2.09  cnf(c_0_22, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 1.91/2.09  cnf(c_0_23, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.91/2.09  cnf(c_0_24, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.91/2.09  cnf(c_0_25, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.91/2.09  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk1_0))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_18]), c_0_18])).
% 1.91/2.09  cnf(c_0_27, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.91/2.09  cnf(c_0_28, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_27])).
% 1.91/2.09  cnf(c_0_29, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,k4_xboole_0(esk1_0,k2_xboole_0(esk3_0,esk2_0))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_28]), c_0_18]), c_0_23]), c_0_18])).
% 1.91/2.09  cnf(c_0_30, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_29])).
% 1.91/2.09  cnf(c_0_31, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.91/2.09  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_30]), c_0_31]), ['proof']).
% 1.91/2.09  # SZS output end CNFRefutation
% 1.91/2.09  # Proof object total steps             : 33
% 1.91/2.09  # Proof object clause steps            : 20
% 1.91/2.09  # Proof object formula steps           : 13
% 1.91/2.09  # Proof object conjectures             : 13
% 1.91/2.09  # Proof object clause conjectures      : 10
% 1.91/2.09  # Proof object formula conjectures     : 3
% 1.91/2.09  # Proof object initial clauses used    : 8
% 1.91/2.09  # Proof object initial formulas used   : 6
% 1.91/2.09  # Proof object generating inferences   : 9
% 1.91/2.09  # Proof object simplifying inferences  : 9
% 1.91/2.09  # Training examples: 0 positive, 0 negative
% 1.91/2.09  # Parsed axioms                        : 12
% 1.91/2.09  # Removed by relevancy pruning/SinE    : 0
% 1.91/2.09  # Initial clauses                      : 15
% 1.91/2.09  # Removed in clause preprocessing      : 1
% 1.91/2.09  # Initial clauses in saturation        : 14
% 1.91/2.09  # Processed clauses                    : 4450
% 1.91/2.09  # ...of these trivial                  : 1859
% 1.91/2.09  # ...subsumed                          : 505
% 1.91/2.09  # ...remaining for further processing  : 2086
% 1.91/2.09  # Other redundant clauses eliminated   : 0
% 1.91/2.09  # Clauses deleted for lack of memory   : 0
% 1.91/2.09  # Backward-subsumed                    : 2
% 1.91/2.09  # Backward-rewritten                   : 205
% 1.91/2.09  # Generated clauses                    : 399793
% 1.91/2.09  # ...of the previous two non-trivial   : 140853
% 1.91/2.09  # Contextual simplify-reflections      : 0
% 1.91/2.09  # Paramodulations                      : 399780
% 1.91/2.09  # Factorizations                       : 0
% 1.91/2.09  # Equation resolutions                 : 13
% 1.91/2.09  # Propositional unsat checks           : 0
% 1.91/2.09  #    Propositional check models        : 0
% 1.91/2.09  #    Propositional check unsatisfiable : 0
% 1.91/2.09  #    Propositional clauses             : 0
% 1.91/2.09  #    Propositional clauses after purity: 0
% 1.91/2.09  #    Propositional unsat core size     : 0
% 1.91/2.09  #    Propositional preprocessing time  : 0.000
% 1.91/2.09  #    Propositional encoding time       : 0.000
% 1.91/2.09  #    Propositional solver time         : 0.000
% 1.91/2.09  #    Success case prop preproc time    : 0.000
% 1.91/2.09  #    Success case prop encoding time   : 0.000
% 1.91/2.09  #    Success case prop solver time     : 0.000
% 1.91/2.09  # Current number of processed clauses  : 1865
% 1.91/2.09  #    Positive orientable unit clauses  : 1801
% 1.91/2.09  #    Positive unorientable unit clauses: 0
% 1.91/2.09  #    Negative unit clauses             : 1
% 1.91/2.09  #    Non-unit-clauses                  : 63
% 1.91/2.09  # Current number of unprocessed clauses: 136258
% 1.91/2.09  # ...number of literals in the above   : 140569
% 1.91/2.09  # Current number of archived formulas  : 0
% 1.91/2.09  # Current number of archived clauses   : 222
% 1.91/2.09  # Clause-clause subsumption calls (NU) : 1305
% 1.91/2.09  # Rec. Clause-clause subsumption calls : 1295
% 1.91/2.09  # Non-unit clause-clause subsumptions  : 507
% 1.91/2.09  # Unit Clause-clause subsumption calls : 177
% 1.91/2.09  # Rewrite failures with RHS unbound    : 0
% 1.91/2.09  # BW rewrite match attempts            : 13794
% 1.91/2.09  # BW rewrite match successes           : 189
% 1.91/2.09  # Condensation attempts                : 0
% 1.91/2.09  # Condensation successes               : 0
% 1.91/2.09  # Termbank termtop insertions          : 5019567
% 1.93/2.10  
% 1.93/2.10  # -------------------------------------------------
% 1.93/2.10  # User time                : 1.669 s
% 1.93/2.10  # System time              : 0.092 s
% 1.93/2.10  # Total time               : 1.761 s
% 1.93/2.10  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:57 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 (  81 expanded)
%              Number of clauses        :   27 (  37 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 153 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X4)
        & r1_xboole_0(X2,X4)
        & r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_xboole_0(X1,X4)
          & r1_xboole_0(X2,X4)
          & r1_xboole_0(X3,X4) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    inference(assume_negation,[status(cth)],[t114_xboole_1])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0)
    & r1_xboole_0(esk2_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_12,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( r1_xboole_0(X16,X17)
      | ~ r1_xboole_0(k3_xboole_0(X16,X17),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

fof(c_0_14,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_15,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_xboole_0(X18,X19)
      | k3_xboole_0(X18,k2_xboole_0(X19,X20)) = k3_xboole_0(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1)) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk1_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk2_0,X1),esk4_0)
    | ~ r1_xboole_0(k3_xboole_0(esk4_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(X1,esk1_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk3_0,X1),esk4_0)
    | ~ r1_xboole_0(k3_xboole_0(esk4_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(X1,k2_xboole_0(esk1_0,esk2_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk2_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.12/0.38  # and selection function SelectDiffNegLit.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.026 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t114_xboole_1, conjecture, ![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 0.12/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.12/0.38  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.12/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.12/0.38  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.12/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.38  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.12/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4))), inference(assume_negation,[status(cth)],[t114_xboole_1])).
% 0.12/0.38  fof(c_0_9, plain, ![X9, X10]:(~r1_xboole_0(X9,X10)|r1_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.12/0.38  fof(c_0_10, negated_conjecture, (((r1_xboole_0(esk1_0,esk4_0)&r1_xboole_0(esk2_0,esk4_0))&r1_xboole_0(esk3_0,esk4_0))&~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.38  fof(c_0_11, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_xboole_0(X14,X15)|r1_xboole_0(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.12/0.38  fof(c_0_12, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.12/0.38  fof(c_0_13, plain, ![X16, X17]:(r1_xboole_0(X16,X17)|~r1_xboole_0(k3_xboole_0(X16,X17),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.12/0.38  fof(c_0_14, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.38  fof(c_0_15, plain, ![X18, X19, X20]:(~r1_xboole_0(X18,X19)|k3_xboole_0(X18,k2_xboole_0(X19,X20))=k3_xboole_0(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.12/0.38  cnf(c_0_16, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_18, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_22, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.38  cnf(c_0_24, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (r1_xboole_0(esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk4_0,k2_xboole_0(esk2_0,X1))=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk1_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.38  fof(c_0_30, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_26])).
% 0.12/0.38  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk2_0,X1),esk4_0)|~r1_xboole_0(k3_xboole_0(esk4_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (r1_xboole_0(k3_xboole_0(X1,esk1_0),esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.12/0.38  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (k3_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.12/0.38  cnf(c_0_37, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_18, c_0_32])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk3_0,X1),esk4_0)|~r1_xboole_0(k3_xboole_0(esk4_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_36])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r1_xboole_0(k3_xboole_0(X1,k2_xboole_0(esk1_0,esk2_0)),esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk2_0)),esk4_0)), inference(rw,[status(thm)],[c_0_39, c_0_35])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 44
% 0.12/0.38  # Proof object clause steps            : 27
% 0.12/0.38  # Proof object formula steps           : 17
% 0.12/0.38  # Proof object conjectures             : 19
% 0.12/0.38  # Proof object clause conjectures      : 16
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 11
% 0.12/0.38  # Proof object initial formulas used   : 8
% 0.12/0.38  # Proof object generating inferences   : 15
% 0.12/0.38  # Proof object simplifying inferences  : 3
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 8
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 11
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 11
% 0.12/0.38  # Processed clauses                    : 247
% 0.12/0.38  # ...of these trivial                  : 29
% 0.12/0.38  # ...subsumed                          : 39
% 0.12/0.38  # ...remaining for further processing  : 179
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 1
% 0.12/0.38  # Generated clauses                    : 1150
% 0.12/0.38  # ...of the previous two non-trivial   : 739
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 1150
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 167
% 0.12/0.38  #    Positive orientable unit clauses  : 125
% 0.12/0.38  #    Positive unorientable unit clauses: 2
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 39
% 0.12/0.38  # Current number of unprocessed clauses: 510
% 0.12/0.38  # ...number of literals in the above   : 607
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 12
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 504
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 504
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 39
% 0.12/0.38  # Unit Clause-clause subsumption calls : 2
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 70
% 0.12/0.38  # BW rewrite match successes           : 12
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 11767
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.041 s
% 0.12/0.39  # System time              : 0.002 s
% 0.12/0.39  # Total time               : 0.043 s
% 0.12/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------

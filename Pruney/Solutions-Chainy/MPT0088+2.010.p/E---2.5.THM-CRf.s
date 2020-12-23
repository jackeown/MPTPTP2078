%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:39 EST 2020

% Result     : Theorem 41.20s
% Output     : CNFRefutation 41.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  51 expanded)
%              Number of clauses        :   17 (  23 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 129 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t81_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_5,plain,(
    ! [X10,X11,X12] :
      ( ( r1_xboole_0(X10,k2_xboole_0(X11,X12))
        | ~ r1_xboole_0(X10,X11)
        | ~ r1_xboole_0(X10,X12) )
      & ( r1_xboole_0(X10,X11)
        | ~ r1_xboole_0(X10,k2_xboole_0(X11,X12)) )
      & ( r1_xboole_0(X10,X12)
        | ~ r1_xboole_0(X10,k2_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_6,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_8,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_14,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))
    | ~ r1_xboole_0(k4_xboole_0(X4,X3),k2_xboole_0(X2,X1))
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
       => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    inference(assume_negation,[status(cth)],[t81_xboole_1])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(k4_xboole_0(X4,X3),X1)
    | ~ r1_xboole_0(k4_xboole_0(X4,X3),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

fof(c_0_18,plain,(
    ! [X13,X14] : r1_xboole_0(k4_xboole_0(X13,X14),X14) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X4)
    | ~ r1_xboole_0(k4_xboole_0(X3,X4),X1)
    | ~ r1_xboole_0(k4_xboole_0(X3,X4),X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_17])).

cnf(c_0_21,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(k4_xboole_0(X3,X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 41.20/41.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 41.20/41.46  # and selection function SelectMaxLComplexAPPNTNp.
% 41.20/41.46  #
% 41.20/41.46  # Preprocessing time       : 0.026 s
% 41.20/41.46  # Presaturation interreduction done
% 41.20/41.46  
% 41.20/41.46  # Proof found!
% 41.20/41.46  # SZS status Theorem
% 41.20/41.46  # SZS output start CNFRefutation
% 41.20/41.46  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 41.20/41.46  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 41.20/41.46  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 41.20/41.46  fof(t81_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 41.20/41.46  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 41.20/41.46  fof(c_0_5, plain, ![X10, X11, X12]:((r1_xboole_0(X10,k2_xboole_0(X11,X12))|~r1_xboole_0(X10,X11)|~r1_xboole_0(X10,X12))&((r1_xboole_0(X10,X11)|~r1_xboole_0(X10,k2_xboole_0(X11,X12)))&(r1_xboole_0(X10,X12)|~r1_xboole_0(X10,k2_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 41.20/41.46  fof(c_0_6, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 41.20/41.46  fof(c_0_7, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 41.20/41.46  cnf(c_0_8, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 41.20/41.46  cnf(c_0_9, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 41.20/41.46  cnf(c_0_10, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 41.20/41.46  cnf(c_0_11, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 41.20/41.46  cnf(c_0_12, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 41.20/41.46  cnf(c_0_13, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_9])).
% 41.20/41.46  cnf(c_0_14, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_xboole_0(X3,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 41.20/41.46  cnf(c_0_15, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))|~r1_xboole_0(k4_xboole_0(X4,X3),k2_xboole_0(X2,X1))|~r1_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 41.20/41.47  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t81_xboole_1])).
% 41.20/41.47  cnf(c_0_17, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X3,X4))|~r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_xboole_0(k4_xboole_0(X4,X3),X1)|~r1_xboole_0(k4_xboole_0(X4,X3),X2)), inference(spm,[status(thm)],[c_0_15, c_0_10])).
% 41.20/41.47  fof(c_0_18, plain, ![X13, X14]:r1_xboole_0(k4_xboole_0(X13,X14),X14), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 41.20/41.47  fof(c_0_19, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))&~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 41.20/41.47  cnf(c_0_20, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_xboole_0(k4_xboole_0(X1,X2),X4)|~r1_xboole_0(k4_xboole_0(X3,X4),X1)|~r1_xboole_0(k4_xboole_0(X3,X4),X2)), inference(spm,[status(thm)],[c_0_8, c_0_17])).
% 41.20/41.47  cnf(c_0_21, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 41.20/41.47  cnf(c_0_22, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 41.20/41.47  cnf(c_0_23, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|~r1_xboole_0(k4_xboole_0(X3,X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_21])])).
% 41.20/41.47  cnf(c_0_24, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_11, c_0_22])).
% 41.20/41.47  cnf(c_0_25, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 41.20/41.47  cnf(c_0_26, negated_conjecture, (~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 41.20/41.47  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_25]), c_0_26]), ['proof']).
% 41.20/41.47  # SZS output end CNFRefutation
% 41.20/41.47  # Proof object total steps             : 28
% 41.20/41.47  # Proof object clause steps            : 17
% 41.20/41.47  # Proof object formula steps           : 11
% 41.20/41.47  # Proof object conjectures             : 8
% 41.20/41.47  # Proof object clause conjectures      : 5
% 41.20/41.47  # Proof object formula conjectures     : 3
% 41.20/41.47  # Proof object initial clauses used    : 7
% 41.20/41.47  # Proof object initial formulas used   : 5
% 41.20/41.47  # Proof object generating inferences   : 10
% 41.20/41.47  # Proof object simplifying inferences  : 3
% 41.20/41.47  # Training examples: 0 positive, 0 negative
% 41.20/41.47  # Parsed axioms                        : 6
% 41.20/41.47  # Removed by relevancy pruning/SinE    : 0
% 41.20/41.47  # Initial clauses                      : 9
% 41.20/41.47  # Removed in clause preprocessing      : 0
% 41.20/41.47  # Initial clauses in saturation        : 9
% 41.20/41.47  # Processed clauses                    : 126226
% 41.20/41.47  # ...of these trivial                  : 1690
% 41.20/41.47  # ...subsumed                          : 114958
% 41.20/41.47  # ...remaining for further processing  : 9578
% 41.20/41.47  # Other redundant clauses eliminated   : 0
% 41.20/41.47  # Clauses deleted for lack of memory   : 227250
% 41.20/41.47  # Backward-subsumed                    : 957
% 41.20/41.47  # Backward-rewritten                   : 7
% 41.20/41.47  # Generated clauses                    : 4486127
% 41.20/41.47  # ...of the previous two non-trivial   : 3993804
% 41.20/41.47  # Contextual simplify-reflections      : 291
% 41.20/41.47  # Paramodulations                      : 4486127
% 41.20/41.47  # Factorizations                       : 0
% 41.20/41.47  # Equation resolutions                 : 0
% 41.20/41.47  # Propositional unsat checks           : 0
% 41.20/41.47  #    Propositional check models        : 0
% 41.20/41.47  #    Propositional check unsatisfiable : 0
% 41.20/41.47  #    Propositional clauses             : 0
% 41.20/41.47  #    Propositional clauses after purity: 0
% 41.20/41.47  #    Propositional unsat core size     : 0
% 41.20/41.47  #    Propositional preprocessing time  : 0.000
% 41.20/41.47  #    Propositional encoding time       : 0.000
% 41.20/41.47  #    Propositional solver time         : 0.000
% 41.20/41.47  #    Success case prop preproc time    : 0.000
% 41.20/41.47  #    Success case prop encoding time   : 0.000
% 41.20/41.47  #    Success case prop solver time     : 0.000
% 41.20/41.47  # Current number of processed clauses  : 8605
% 41.20/41.47  #    Positive orientable unit clauses  : 927
% 41.20/41.47  #    Positive unorientable unit clauses: 1
% 41.20/41.47  #    Negative unit clauses             : 10
% 41.20/41.47  #    Non-unit-clauses                  : 7667
% 41.20/41.47  # Current number of unprocessed clauses: 1470099
% 41.20/41.47  # ...number of literals in the above   : 4360613
% 41.20/41.47  # Current number of archived formulas  : 0
% 41.20/41.47  # Current number of archived clauses   : 973
% 41.20/41.47  # Clause-clause subsumption calls (NU) : 14515610
% 41.20/41.47  # Rec. Clause-clause subsumption calls : 12401775
% 41.20/41.47  # Non-unit clause-clause subsumptions  : 113978
% 41.20/41.47  # Unit Clause-clause subsumption calls : 127869
% 41.20/41.47  # Rewrite failures with RHS unbound    : 0
% 41.20/41.47  # BW rewrite match attempts            : 101731
% 41.20/41.47  # BW rewrite match successes           : 13
% 41.20/41.47  # Condensation attempts                : 0
% 41.20/41.47  # Condensation successes               : 0
% 41.20/41.47  # Termbank termtop insertions          : 101292361
% 41.33/41.55  
% 41.33/41.55  # -------------------------------------------------
% 41.33/41.55  # User time                : 40.156 s
% 41.33/41.55  # System time              : 1.019 s
% 41.33/41.55  # Total time               : 41.175 s
% 41.33/41.55  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------

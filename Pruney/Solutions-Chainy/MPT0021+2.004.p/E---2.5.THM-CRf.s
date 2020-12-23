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
% DateTime   : Thu Dec  3 10:31:50 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  55 expanded)
%              Number of clauses        :   17 (  23 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 127 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2)
          & ! [X4] :
              ( ( r1_tarski(X1,X4)
                & r1_tarski(X3,X4) )
             => r1_tarski(X2,X4) ) )
       => X2 = k2_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t14_xboole_1])).

fof(c_0_6,negated_conjecture,(
    ! [X17] :
      ( r1_tarski(esk1_0,esk2_0)
      & r1_tarski(esk3_0,esk2_0)
      & ( ~ r1_tarski(esk1_0,X17)
        | ~ r1_tarski(esk3_0,X17)
        | r1_tarski(esk2_0,X17) )
      & esk2_0 != k2_xboole_0(esk1_0,esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X12,X13] : r1_tarski(X12,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_8,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | k2_xboole_0(X7,X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk3_0,X1))
    | ~ r1_tarski(esk1_0,k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk1_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0)) = k2_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_xboole_0(esk1_0,X1)) = k2_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 != k2_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:43:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 0.22/0.39  # and selection function SelectMaxLComplexAPPNTNp.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.026 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(t14_xboole_1, conjecture, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.22/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.22/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.22/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.22/0.39  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.22/0.39  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t14_xboole_1])).
% 0.22/0.39  fof(c_0_6, negated_conjecture, ![X17]:(((r1_tarski(esk1_0,esk2_0)&r1_tarski(esk3_0,esk2_0))&(~r1_tarski(esk1_0,X17)|~r1_tarski(esk3_0,X17)|r1_tarski(esk2_0,X17)))&esk2_0!=k2_xboole_0(esk1_0,esk3_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.22/0.39  fof(c_0_7, plain, ![X12, X13]:r1_tarski(X12,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.22/0.39  fof(c_0_8, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.22/0.39  cnf(c_0_9, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(esk1_0,X1)|~r1_tarski(esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.39  cnf(c_0_10, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.22/0.39  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.39  fof(c_0_12, plain, ![X7, X8]:(~r1_tarski(X7,X8)|k2_xboole_0(X7,X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.22/0.39  cnf(c_0_13, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk3_0,X1))|~r1_tarski(esk1_0,k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.22/0.39  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.22/0.39  fof(c_0_15, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.22/0.39  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.39  cnf(c_0_17, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.39  cnf(c_0_18, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.39  cnf(c_0_19, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_11])).
% 0.22/0.39  cnf(c_0_20, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk2_0,esk1_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11])).
% 0.22/0.39  cnf(c_0_22, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_16, c_0_18])).
% 0.22/0.39  cnf(c_0_23, negated_conjecture, (k2_xboole_0(esk2_0,k2_xboole_0(esk1_0,esk3_0))=k2_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_19])).
% 0.22/0.39  cnf(c_0_24, negated_conjecture, (k2_xboole_0(esk2_0,k2_xboole_0(esk1_0,X1))=k2_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.22/0.39  cnf(c_0_25, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0), inference(rw,[status(thm)],[c_0_22, c_0_11])).
% 0.22/0.39  cnf(c_0_26, negated_conjecture, (esk2_0!=k2_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.39  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 28
% 0.22/0.39  # Proof object clause steps            : 17
% 0.22/0.39  # Proof object formula steps           : 11
% 0.22/0.39  # Proof object conjectures             : 15
% 0.22/0.39  # Proof object clause conjectures      : 12
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 8
% 0.22/0.39  # Proof object initial formulas used   : 5
% 0.22/0.39  # Proof object generating inferences   : 7
% 0.22/0.39  # Proof object simplifying inferences  : 6
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 5
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 8
% 0.22/0.39  # Removed in clause preprocessing      : 0
% 0.22/0.39  # Initial clauses in saturation        : 8
% 0.22/0.39  # Processed clauses                    : 40
% 0.22/0.39  # ...of these trivial                  : 2
% 0.22/0.39  # ...subsumed                          : 5
% 0.22/0.39  # ...remaining for further processing  : 33
% 0.22/0.39  # Other redundant clauses eliminated   : 0
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 4
% 0.22/0.39  # Generated clauses                    : 103
% 0.22/0.39  # ...of the previous two non-trivial   : 59
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 103
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 0
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 21
% 0.22/0.39  #    Positive orientable unit clauses  : 15
% 0.22/0.39  #    Positive unorientable unit clauses: 1
% 0.22/0.39  #    Negative unit clauses             : 1
% 0.22/0.39  #    Non-unit-clauses                  : 4
% 0.22/0.39  # Current number of unprocessed clauses: 34
% 0.22/0.39  # ...number of literals in the above   : 35
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 12
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 17
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 17
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.22/0.39  # Unit Clause-clause subsumption calls : 2
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 27
% 0.22/0.39  # BW rewrite match successes           : 20
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 1273
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.024 s
% 0.22/0.39  # System time              : 0.007 s
% 0.22/0.39  # Total time               : 0.031 s
% 0.22/0.39  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

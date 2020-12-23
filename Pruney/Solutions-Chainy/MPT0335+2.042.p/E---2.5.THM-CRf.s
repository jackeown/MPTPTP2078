%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:45 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   28 (  44 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 ( 106 expanded)
%              Number of equality atoms :   23 (  50 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X43,X44,X45] :
      ( ( r2_hidden(X43,X45)
        | ~ r1_tarski(k2_tarski(X43,X44),X45) )
      & ( r2_hidden(X44,X45)
        | ~ r1_tarski(k2_tarski(X43,X44),X45) )
      & ( ~ r2_hidden(X43,X45)
        | ~ r2_hidden(X44,X45)
        | r1_tarski(k2_tarski(X43,X44),X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_8,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0)
    & r2_hidden(esk4_0,esk1_0)
    & k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k3_xboole_0(X13,X14) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X10,X11,X12] : k3_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_tarski(X1,esk4_0),esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_19,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k1_tarski(esk4_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_11]),c_0_17])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(esk1_0,k1_tarski(esk4_0)) = k1_tarski(esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.30  % Computer   : n014.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 15:32:07 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  # Version: 2.5pre002
% 0.11/0.30  # No SInE strategy applied
% 0.11/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.33  # AutoSched0-Mode selected heuristic H_____047_C09_12_F1_AE_ND_CS_SP_S5PRR_S2S
% 0.15/0.33  # and selection function SelectNewComplexAHP.
% 0.15/0.33  #
% 0.15/0.33  # Preprocessing time       : 0.027 s
% 0.15/0.33  # Presaturation interreduction done
% 0.15/0.33  
% 0.15/0.33  # Proof found!
% 0.15/0.33  # SZS status Theorem
% 0.15/0.33  # SZS output start CNFRefutation
% 0.15/0.33  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.15/0.33  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.15/0.33  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.15/0.33  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.15/0.33  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.15/0.33  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.15/0.33  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.15/0.33  fof(c_0_7, plain, ![X43, X44, X45]:(((r2_hidden(X43,X45)|~r1_tarski(k2_tarski(X43,X44),X45))&(r2_hidden(X44,X45)|~r1_tarski(k2_tarski(X43,X44),X45)))&(~r2_hidden(X43,X45)|~r2_hidden(X44,X45)|r1_tarski(k2_tarski(X43,X44),X45))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.15/0.33  fof(c_0_8, negated_conjecture, (((r1_tarski(esk1_0,esk2_0)&k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0))&r2_hidden(esk4_0,esk1_0))&k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.15/0.33  fof(c_0_9, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k3_xboole_0(X13,X14)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.15/0.33  cnf(c_0_10, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.33  cnf(c_0_11, negated_conjecture, (r2_hidden(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.33  fof(c_0_12, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.15/0.33  fof(c_0_13, plain, ![X10, X11, X12]:k3_xboole_0(k3_xboole_0(X10,X11),X12)=k3_xboole_0(X10,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.15/0.33  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.33  cnf(c_0_15, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.33  cnf(c_0_16, negated_conjecture, (r1_tarski(k2_tarski(X1,esk4_0),esk1_0)|~r2_hidden(X1,esk1_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.15/0.33  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.33  fof(c_0_18, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.15/0.33  cnf(c_0_19, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_20, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.15/0.33  cnf(c_0_21, negated_conjecture, (r1_tarski(k1_tarski(esk4_0),esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_11]), c_0_17])).
% 0.15/0.33  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.33  cnf(c_0_23, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1))=k3_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.15/0.33  cnf(c_0_24, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.33  cnf(c_0_25, negated_conjecture, (k3_xboole_0(esk1_0,k1_tarski(esk4_0))=k1_tarski(esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_21]), c_0_22])).
% 0.15/0.33  cnf(c_0_26, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.33  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), ['proof']).
% 0.15/0.33  # SZS output end CNFRefutation
% 0.15/0.33  # Proof object total steps             : 28
% 0.15/0.33  # Proof object clause steps            : 15
% 0.15/0.33  # Proof object formula steps           : 13
% 0.15/0.33  # Proof object conjectures             : 13
% 0.15/0.33  # Proof object clause conjectures      : 10
% 0.15/0.33  # Proof object formula conjectures     : 3
% 0.15/0.33  # Proof object initial clauses used    : 9
% 0.15/0.33  # Proof object initial formulas used   : 6
% 0.15/0.33  # Proof object generating inferences   : 6
% 0.15/0.33  # Proof object simplifying inferences  : 4
% 0.15/0.33  # Training examples: 0 positive, 0 negative
% 0.15/0.33  # Parsed axioms                        : 12
% 0.15/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.33  # Initial clauses                      : 17
% 0.15/0.33  # Removed in clause preprocessing      : 0
% 0.15/0.33  # Initial clauses in saturation        : 17
% 0.15/0.33  # Processed clauses                    : 43
% 0.15/0.33  # ...of these trivial                  : 2
% 0.15/0.33  # ...subsumed                          : 1
% 0.15/0.33  # ...remaining for further processing  : 39
% 0.15/0.33  # Other redundant clauses eliminated   : 0
% 0.15/0.33  # Clauses deleted for lack of memory   : 0
% 0.15/0.33  # Backward-subsumed                    : 0
% 0.15/0.33  # Backward-rewritten                   : 0
% 0.15/0.33  # Generated clauses                    : 29
% 0.15/0.33  # ...of the previous two non-trivial   : 23
% 0.15/0.33  # Contextual simplify-reflections      : 0
% 0.15/0.33  # Paramodulations                      : 29
% 0.15/0.33  # Factorizations                       : 0
% 0.15/0.33  # Equation resolutions                 : 0
% 0.15/0.33  # Propositional unsat checks           : 0
% 0.15/0.33  #    Propositional check models        : 0
% 0.15/0.33  #    Propositional check unsatisfiable : 0
% 0.15/0.33  #    Propositional clauses             : 0
% 0.15/0.33  #    Propositional clauses after purity: 0
% 0.15/0.33  #    Propositional unsat core size     : 0
% 0.15/0.33  #    Propositional preprocessing time  : 0.000
% 0.15/0.33  #    Propositional encoding time       : 0.000
% 0.15/0.33  #    Propositional solver time         : 0.000
% 0.15/0.33  #    Success case prop preproc time    : 0.000
% 0.15/0.33  #    Success case prop encoding time   : 0.000
% 0.15/0.33  #    Success case prop solver time     : 0.000
% 0.15/0.33  # Current number of processed clauses  : 22
% 0.15/0.33  #    Positive orientable unit clauses  : 14
% 0.15/0.33  #    Positive unorientable unit clauses: 1
% 0.15/0.33  #    Negative unit clauses             : 1
% 0.15/0.33  #    Non-unit-clauses                  : 6
% 0.15/0.33  # Current number of unprocessed clauses: 14
% 0.15/0.33  # ...number of literals in the above   : 14
% 0.15/0.33  # Current number of archived formulas  : 0
% 0.15/0.33  # Current number of archived clauses   : 17
% 0.15/0.33  # Clause-clause subsumption calls (NU) : 9
% 0.15/0.33  # Rec. Clause-clause subsumption calls : 7
% 0.15/0.33  # Non-unit clause-clause subsumptions  : 1
% 0.15/0.33  # Unit Clause-clause subsumption calls : 3
% 0.15/0.33  # Rewrite failures with RHS unbound    : 0
% 0.15/0.33  # BW rewrite match attempts            : 18
% 0.15/0.33  # BW rewrite match successes           : 16
% 0.15/0.33  # Condensation attempts                : 0
% 0.15/0.33  # Condensation successes               : 0
% 0.15/0.33  # Termbank termtop insertions          : 1186
% 0.15/0.33  
% 0.15/0.33  # -------------------------------------------------
% 0.15/0.33  # User time                : 0.028 s
% 0.15/0.33  # System time              : 0.003 s
% 0.15/0.33  # Total time               : 0.031 s
% 0.15/0.33  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------

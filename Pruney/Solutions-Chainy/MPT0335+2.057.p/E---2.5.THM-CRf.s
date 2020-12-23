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
% DateTime   : Thu Dec  3 10:44:47 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   20 (  29 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  71 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k3_xboole_0(X8,X9) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0)
    & r2_hidden(esk4_0,esk1_0)
    & k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7] : k3_xboole_0(k3_xboole_0(X5,X6),X7) = k3_xboole_0(X5,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_8,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | k3_xboole_0(X11,k1_tarski(X10)) = k1_tarski(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

cnf(c_0_11,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( k3_xboole_0(esk1_0,k1_tarski(esk4_0)) = k1_tarski(esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.13/0.37  # and selection function PSelectSmallestOrientable.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.025 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.13/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.37  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.13/0.37  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.13/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.13/0.37  fof(c_0_5, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k3_xboole_0(X8,X9)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, (((r1_tarski(esk1_0,esk2_0)&k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0))&r2_hidden(esk4_0,esk1_0))&k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X5, X6, X7]:k3_xboole_0(k3_xboole_0(X5,X6),X7)=k3_xboole_0(X5,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.13/0.37  cnf(c_0_8, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_10, plain, ![X10, X11]:(~r2_hidden(X10,X11)|k3_xboole_0(X11,k1_tarski(X10))=k1_tarski(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.13/0.37  cnf(c_0_11, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.13/0.37  cnf(c_0_13, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (r2_hidden(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1))=k3_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (k3_xboole_0(esk1_0,k1_tarski(esk4_0))=k1_tarski(esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 20
% 0.13/0.37  # Proof object clause steps            : 11
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 7
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 4
% 0.13/0.37  # Proof object simplifying inferences  : 2
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 7
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 7
% 0.13/0.37  # Processed clauses                    : 19
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 19
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 20
% 0.13/0.37  # ...of the previous two non-trivial   : 17
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 20
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 12
% 0.13/0.37  #    Positive orientable unit clauses  : 7
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 4
% 0.13/0.37  # Current number of unprocessed clauses: 9
% 0.13/0.37  # ...number of literals in the above   : 16
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 7
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 1
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 608
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.025 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.029 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

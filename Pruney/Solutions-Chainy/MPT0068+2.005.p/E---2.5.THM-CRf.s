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
% DateTime   : Thu Dec  3 10:32:34 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t61_xboole_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( ( k4_xboole_0(X5,X6) != k1_xboole_0
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | k4_xboole_0(X5,X6) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_5,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => r2_xboole_0(k1_xboole_0,X1) ) ),
    inference(assume_negation,[status(cth)],[t61_xboole_1])).

fof(c_0_7,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | ~ r2_xboole_0(X3,X4) )
      & ( X3 != X4
        | ~ r2_xboole_0(X3,X4) )
      & ( ~ r1_tarski(X3,X4)
        | X3 = X4
        | r2_xboole_0(X3,X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & ~ r2_xboole_0(k1_xboole_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_xboole_0(k1_xboole_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:26:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.18/0.36  # and selection function SelectNewComplexAHPNS.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.026 s
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.36  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.18/0.36  fof(t61_xboole_1, conjecture, ![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 0.18/0.36  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.18/0.36  fof(c_0_4, plain, ![X5, X6]:((k4_xboole_0(X5,X6)!=k1_xboole_0|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|k4_xboole_0(X5,X6)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.36  fof(c_0_5, plain, ![X7]:k4_xboole_0(k1_xboole_0,X7)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.18/0.36  fof(c_0_6, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1))), inference(assume_negation,[status(cth)],[t61_xboole_1])).
% 0.18/0.36  fof(c_0_7, plain, ![X3, X4]:(((r1_tarski(X3,X4)|~r2_xboole_0(X3,X4))&(X3!=X4|~r2_xboole_0(X3,X4)))&(~r1_tarski(X3,X4)|X3=X4|r2_xboole_0(X3,X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.18/0.36  cnf(c_0_8, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.18/0.36  cnf(c_0_9, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.36  fof(c_0_10, negated_conjecture, (esk1_0!=k1_xboole_0&~r2_xboole_0(k1_xboole_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.18/0.36  cnf(c_0_11, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_12, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.18/0.36  cnf(c_0_13, negated_conjecture, (~r2_xboole_0(k1_xboole_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_14, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 17
% 0.18/0.36  # Proof object clause steps            : 8
% 0.18/0.36  # Proof object formula steps           : 9
% 0.18/0.36  # Proof object conjectures             : 6
% 0.18/0.36  # Proof object clause conjectures      : 3
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 5
% 0.18/0.36  # Proof object initial formulas used   : 4
% 0.18/0.36  # Proof object generating inferences   : 3
% 0.18/0.36  # Proof object simplifying inferences  : 1
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 4
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 8
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 8
% 0.18/0.36  # Processed clauses                    : 11
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 11
% 0.18/0.36  # Other redundant clauses eliminated   : 1
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 0
% 0.18/0.36  # Generated clauses                    : 6
% 0.18/0.36  # ...of the previous two non-trivial   : 3
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 5
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 1
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 10
% 0.18/0.36  #    Positive orientable unit clauses  : 2
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 3
% 0.18/0.36  #    Non-unit-clauses                  : 5
% 0.18/0.36  # Current number of unprocessed clauses: 0
% 0.18/0.36  # ...number of literals in the above   : 0
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 0
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.36  # Unit Clause-clause subsumption calls : 2
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 0
% 0.18/0.36  # BW rewrite match successes           : 0
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 353
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.026 s
% 0.18/0.36  # System time              : 0.003 s
% 0.18/0.36  # Total time               : 0.029 s
% 0.18/0.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

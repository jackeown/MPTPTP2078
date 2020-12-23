%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:41 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  43 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t150_relat_1,conjecture,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_7,plain,(
    ! [X4] : v1_relat_1(k6_relat_1(X4)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_8,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(k1_relat_1(X8),X7)
      | k7_relat_1(X8,X7) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_9,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_11,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t150_relat_1])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | k2_relat_1(k7_relat_1(X6,X5)) = k9_relat_1(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_14,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_16,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,negated_conjecture,(
    k9_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_19,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_21,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_22,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.12/0.38  # and selection function SelectCQPrecWNTNp.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.038 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.12/0.38  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.12/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(t150_relat_1, conjecture, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 0.12/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.12/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.12/0.38  fof(c_0_7, plain, ![X4]:v1_relat_1(k6_relat_1(X4)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.12/0.38  fof(c_0_8, plain, ![X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(k1_relat_1(X8),X7)|k7_relat_1(X8,X7)=X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.12/0.38  cnf(c_0_9, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.12/0.38  fof(c_0_11, plain, ![X3]:r1_tarski(k1_xboole_0,X3), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t150_relat_1])).
% 0.12/0.38  fof(c_0_13, plain, ![X5, X6]:(~v1_relat_1(X6)|k2_relat_1(k7_relat_1(X6,X5))=k9_relat_1(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.12/0.38  cnf(c_0_14, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_15, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.38  cnf(c_0_16, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.38  cnf(c_0_17, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_18, negated_conjecture, k9_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.38  cnf(c_0_19, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_20, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 0.12/0.38  cnf(c_0_21, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (k9_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_23, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_16])])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 25
% 0.12/0.38  # Proof object clause steps            : 12
% 0.12/0.38  # Proof object formula steps           : 13
% 0.12/0.38  # Proof object conjectures             : 5
% 0.12/0.38  # Proof object clause conjectures      : 2
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 8
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 3
% 0.12/0.38  # Proof object simplifying inferences  : 8
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 7
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 8
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 8
% 0.12/0.38  # Processed clauses                    : 19
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 19
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 1
% 0.12/0.38  # Generated clauses                    : 3
% 0.12/0.38  # ...of the previous two non-trivial   : 3
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 3
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
% 0.12/0.38  # Current number of processed clauses  : 10
% 0.12/0.38  #    Positive orientable unit clauses  : 8
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 2
% 0.12/0.38  # Current number of unprocessed clauses: 0
% 0.12/0.38  # ...number of literals in the above   : 0
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 9
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.38  # Unit Clause-clause subsumption calls : 0
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 383
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.041 s
% 0.12/0.38  # System time              : 0.002 s
% 0.12/0.38  # Total time               : 0.043 s
% 0.12/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:09 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 (  59 expanded)
%              Number of clauses        :   17 (  24 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 155 expanded)
%              Number of equality atoms :   23 (  68 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc18_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X2) )
     => ( v1_xboole_0(k8_relat_1(X2,X1))
        & v1_relat_1(k8_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).

fof(t126_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k2_relat_1(X1),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(t197_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( k2_relat_1(X1) = k1_xboole_0
              & k2_relat_1(X2) = k1_xboole_0 )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

fof(fc13_subset_1,axiom,(
    ! [X1] : v1_xboole_0(k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( ( v1_xboole_0(k8_relat_1(X7,X6))
        | ~ v1_relat_1(X6)
        | ~ v1_xboole_0(X7) )
      & ( v1_relat_1(k8_relat_1(X7,X6))
        | ~ v1_relat_1(X6)
        | ~ v1_xboole_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc18_relat_1])])])).

fof(c_0_7,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k8_relat_1(k2_relat_1(X8),X8) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( k2_relat_1(X1) = k1_xboole_0
                & k2_relat_1(X2) = k1_xboole_0 )
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t197_relat_1])).

fof(c_0_9,plain,(
    ! [X5] : v1_xboole_0(k1_subset_1(X5)) ),
    inference(variable_rename,[status(thm)],[fc13_subset_1])).

fof(c_0_10,plain,(
    ! [X4] : k1_subset_1(X4) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_11,plain,
    ( v1_xboole_0(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & k2_relat_1(esk1_0) = k1_xboole_0
    & k2_relat_1(esk2_0) = k1_xboole_0
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23]),c_0_24]),c_0_20])])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:57:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.14/0.37  # and selection function SelectCQPrecWNTNp.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(fc18_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_xboole_0(X2))=>(v1_xboole_0(k8_relat_1(X2,X1))&v1_relat_1(k8_relat_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc18_relat_1)).
% 0.14/0.37  fof(t126_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k2_relat_1(X1),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 0.14/0.37  fof(t197_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((k2_relat_1(X1)=k1_xboole_0&k2_relat_1(X2)=k1_xboole_0)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t197_relat_1)).
% 0.14/0.37  fof(fc13_subset_1, axiom, ![X1]:v1_xboole_0(k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 0.14/0.37  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.14/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.37  fof(c_0_6, plain, ![X6, X7]:((v1_xboole_0(k8_relat_1(X7,X6))|(~v1_relat_1(X6)|~v1_xboole_0(X7)))&(v1_relat_1(k8_relat_1(X7,X6))|(~v1_relat_1(X6)|~v1_xboole_0(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc18_relat_1])])])).
% 0.14/0.37  fof(c_0_7, plain, ![X8]:(~v1_relat_1(X8)|k8_relat_1(k2_relat_1(X8),X8)=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).
% 0.14/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((k2_relat_1(X1)=k1_xboole_0&k2_relat_1(X2)=k1_xboole_0)=>X1=X2)))), inference(assume_negation,[status(cth)],[t197_relat_1])).
% 0.14/0.37  fof(c_0_9, plain, ![X5]:v1_xboole_0(k1_subset_1(X5)), inference(variable_rename,[status(thm)],[fc13_subset_1])).
% 0.14/0.37  fof(c_0_10, plain, ![X4]:k1_subset_1(X4)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.14/0.37  cnf(c_0_11, plain, (v1_xboole_0(k8_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_12, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  fof(c_0_13, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&((k2_relat_1(esk1_0)=k1_xboole_0&k2_relat_1(esk2_0)=k1_xboole_0)&esk1_0!=esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.14/0.37  cnf(c_0_14, plain, (v1_xboole_0(k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_15, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  fof(c_0_16, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.37  cnf(c_0_17, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (k2_relat_1(esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_20, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.37  cnf(c_0_21, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (v1_xboole_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_23]), c_0_24]), c_0_20])])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (esk1_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.37  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_27]), c_0_28]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 30
% 0.14/0.37  # Proof object clause steps            : 17
% 0.14/0.37  # Proof object formula steps           : 13
% 0.14/0.37  # Proof object conjectures             : 13
% 0.14/0.37  # Proof object clause conjectures      : 10
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 10
% 0.14/0.37  # Proof object initial formulas used   : 6
% 0.14/0.37  # Proof object generating inferences   : 5
% 0.14/0.37  # Proof object simplifying inferences  : 9
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 6
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 11
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 10
% 0.14/0.37  # Processed clauses                    : 29
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 29
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 4
% 0.14/0.37  # Generated clauses                    : 15
% 0.14/0.37  # ...of the previous two non-trivial   : 12
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 15
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 15
% 0.14/0.37  #    Positive orientable unit clauses  : 9
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 5
% 0.14/0.37  # Current number of unprocessed clauses: 2
% 0.14/0.37  # ...number of literals in the above   : 4
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 15
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 11
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 11
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 0
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 1
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 631
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.026 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.030 s
% 0.14/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

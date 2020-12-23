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
% DateTime   : Thu Dec  3 10:49:23 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc14_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ( v1_xboole_0(k4_relat_1(X1))
        & v1_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

fof(t66_relat_1,conjecture,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_4,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | X2 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_5,plain,(
    ! [X3] :
      ( ( v1_xboole_0(k4_relat_1(X3))
        | ~ v1_xboole_0(X3) )
      & ( v1_relat_1(k4_relat_1(X3))
        | ~ v1_xboole_0(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_relat_1])])])).

fof(c_0_6,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t66_relat_1])).

cnf(c_0_7,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_xboole_0(k4_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_12,negated_conjecture,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.27  % Computer   : n014.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 14:30:37 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  # Version: 2.5pre002
% 0.08/0.27  # No SInE strategy applied
% 0.08/0.27  # Trying AutoSched0 for 299 seconds
% 0.08/0.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S08BI
% 0.08/0.29  # and selection function SelectCQPrecWNTNp.
% 0.08/0.29  #
% 0.08/0.29  # Preprocessing time       : 0.015 s
% 0.08/0.29  # Presaturation interreduction done
% 0.08/0.29  
% 0.08/0.29  # Proof found!
% 0.08/0.29  # SZS status Theorem
% 0.08/0.29  # SZS output start CNFRefutation
% 0.08/0.29  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.08/0.29  fof(fc14_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>(v1_xboole_0(k4_relat_1(X1))&v1_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 0.08/0.29  fof(t66_relat_1, conjecture, k4_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 0.08/0.29  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.08/0.29  fof(c_0_4, plain, ![X2]:(~v1_xboole_0(X2)|X2=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.08/0.29  fof(c_0_5, plain, ![X3]:((v1_xboole_0(k4_relat_1(X3))|~v1_xboole_0(X3))&(v1_relat_1(k4_relat_1(X3))|~v1_xboole_0(X3))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_relat_1])])])).
% 0.08/0.29  fof(c_0_6, negated_conjecture, ~(k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t66_relat_1])).
% 0.08/0.29  cnf(c_0_7, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.08/0.29  cnf(c_0_8, plain, (v1_xboole_0(k4_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.08/0.29  fof(c_0_9, negated_conjecture, k4_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_6])).
% 0.08/0.29  cnf(c_0_10, plain, (k4_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.08/0.29  cnf(c_0_11, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.08/0.29  cnf(c_0_12, negated_conjecture, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.29  cnf(c_0_13, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), ['proof']).
% 0.08/0.29  # SZS output end CNFRefutation
% 0.08/0.29  # Proof object total steps             : 14
% 0.08/0.29  # Proof object clause steps            : 6
% 0.08/0.29  # Proof object formula steps           : 8
% 0.08/0.29  # Proof object conjectures             : 4
% 0.08/0.29  # Proof object clause conjectures      : 1
% 0.08/0.29  # Proof object formula conjectures     : 3
% 0.08/0.29  # Proof object initial clauses used    : 4
% 0.08/0.29  # Proof object initial formulas used   : 4
% 0.08/0.29  # Proof object generating inferences   : 2
% 0.08/0.29  # Proof object simplifying inferences  : 1
% 0.08/0.29  # Training examples: 0 positive, 0 negative
% 0.08/0.29  # Parsed axioms                        : 4
% 0.08/0.29  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.29  # Initial clauses                      : 5
% 0.08/0.29  # Removed in clause preprocessing      : 0
% 0.08/0.29  # Initial clauses in saturation        : 5
% 0.08/0.29  # Processed clauses                    : 11
% 0.08/0.29  # ...of these trivial                  : 0
% 0.08/0.29  # ...subsumed                          : 0
% 0.08/0.29  # ...remaining for further processing  : 11
% 0.08/0.29  # Other redundant clauses eliminated   : 0
% 0.08/0.29  # Clauses deleted for lack of memory   : 0
% 0.08/0.29  # Backward-subsumed                    : 0
% 0.08/0.29  # Backward-rewritten                   : 0
% 0.08/0.29  # Generated clauses                    : 3
% 0.08/0.29  # ...of the previous two non-trivial   : 2
% 0.08/0.29  # Contextual simplify-reflections      : 0
% 0.08/0.29  # Paramodulations                      : 3
% 0.08/0.29  # Factorizations                       : 0
% 0.08/0.29  # Equation resolutions                 : 0
% 0.08/0.29  # Propositional unsat checks           : 0
% 0.08/0.29  #    Propositional check models        : 0
% 0.08/0.29  #    Propositional check unsatisfiable : 0
% 0.08/0.29  #    Propositional clauses             : 0
% 0.08/0.29  #    Propositional clauses after purity: 0
% 0.08/0.29  #    Propositional unsat core size     : 0
% 0.08/0.29  #    Propositional preprocessing time  : 0.000
% 0.08/0.29  #    Propositional encoding time       : 0.000
% 0.08/0.29  #    Propositional solver time         : 0.000
% 0.08/0.29  #    Success case prop preproc time    : 0.000
% 0.08/0.29  #    Success case prop encoding time   : 0.000
% 0.08/0.29  #    Success case prop solver time     : 0.000
% 0.08/0.29  # Current number of processed clauses  : 6
% 0.08/0.29  #    Positive orientable unit clauses  : 1
% 0.08/0.29  #    Positive unorientable unit clauses: 0
% 0.08/0.29  #    Negative unit clauses             : 1
% 0.08/0.29  #    Non-unit-clauses                  : 4
% 0.08/0.29  # Current number of unprocessed clauses: 0
% 0.08/0.29  # ...number of literals in the above   : 0
% 0.08/0.29  # Current number of archived formulas  : 0
% 0.08/0.29  # Current number of archived clauses   : 5
% 0.08/0.29  # Clause-clause subsumption calls (NU) : 1
% 0.08/0.29  # Rec. Clause-clause subsumption calls : 1
% 0.08/0.29  # Non-unit clause-clause subsumptions  : 0
% 0.08/0.29  # Unit Clause-clause subsumption calls : 0
% 0.08/0.29  # Rewrite failures with RHS unbound    : 0
% 0.08/0.29  # BW rewrite match attempts            : 0
% 0.08/0.29  # BW rewrite match successes           : 0
% 0.08/0.29  # Condensation attempts                : 0
% 0.08/0.29  # Condensation successes               : 0
% 0.08/0.29  # Termbank termtop insertions          : 231
% 0.08/0.29  
% 0.08/0.29  # -------------------------------------------------
% 0.08/0.29  # User time                : 0.016 s
% 0.08/0.29  # System time              : 0.001 s
% 0.08/0.29  # Total time               : 0.017 s
% 0.08/0.29  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------

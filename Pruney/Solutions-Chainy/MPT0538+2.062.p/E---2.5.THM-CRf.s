%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:26 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t138_relat_1,conjecture,(
    ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_6,plain,(
    ! [X4,X5] :
      ( ( k2_zfmisc_1(X4,X5) != k1_xboole_0
        | X4 = k1_xboole_0
        | X5 = k1_xboole_0 )
      & ( X4 != k1_xboole_0
        | k2_zfmisc_1(X4,X5) = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X4,X5) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(k2_relat_1(X9),X8)
      | k8_relat_1(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

fof(c_0_8,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_9,plain,(
    ! [X6,X7] : v1_relat_1(k2_zfmisc_1(X6,X7)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t138_relat_1])).

cnf(c_0_12,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,(
    k8_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k8_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.27  % Computer   : n021.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 15:58:49 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  # Version: 2.5pre002
% 0.08/0.27  # No SInE strategy applied
% 0.08/0.27  # Trying AutoSched0 for 299 seconds
% 0.08/0.30  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.08/0.30  # and selection function SelectDiffNegLit.
% 0.08/0.30  #
% 0.08/0.30  # Preprocessing time       : 0.026 s
% 0.08/0.30  # Presaturation interreduction done
% 0.08/0.30  
% 0.08/0.30  # Proof found!
% 0.08/0.30  # SZS status Theorem
% 0.08/0.30  # SZS output start CNFRefutation
% 0.08/0.30  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.08/0.30  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 0.08/0.30  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.08/0.30  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.08/0.30  fof(t138_relat_1, conjecture, ![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 0.08/0.30  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.08/0.30  fof(c_0_6, plain, ![X4, X5]:((k2_zfmisc_1(X4,X5)!=k1_xboole_0|(X4=k1_xboole_0|X5=k1_xboole_0))&((X4!=k1_xboole_0|k2_zfmisc_1(X4,X5)=k1_xboole_0)&(X5!=k1_xboole_0|k2_zfmisc_1(X4,X5)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.08/0.30  fof(c_0_7, plain, ![X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(k2_relat_1(X9),X8)|k8_relat_1(X8,X9)=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.08/0.30  fof(c_0_8, plain, ![X3]:r1_tarski(k1_xboole_0,X3), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.08/0.30  fof(c_0_9, plain, ![X6, X7]:v1_relat_1(k2_zfmisc_1(X6,X7)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.08/0.30  cnf(c_0_10, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.08/0.30  fof(c_0_11, negated_conjecture, ~(![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t138_relat_1])).
% 0.08/0.30  cnf(c_0_12, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.08/0.30  cnf(c_0_13, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.08/0.30  cnf(c_0_14, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.30  cnf(c_0_15, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.30  cnf(c_0_16, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_10])).
% 0.08/0.30  fof(c_0_17, negated_conjecture, k8_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.08/0.30  cnf(c_0_18, plain, (k8_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.08/0.30  cnf(c_0_19, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.08/0.30  cnf(c_0_20, negated_conjecture, (k8_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.08/0.30  cnf(c_0_21, plain, (k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])])).
% 0.08/0.30  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])]), ['proof']).
% 0.08/0.30  # SZS output end CNFRefutation
% 0.08/0.30  # Proof object total steps             : 23
% 0.08/0.30  # Proof object clause steps            : 11
% 0.08/0.30  # Proof object formula steps           : 12
% 0.08/0.30  # Proof object conjectures             : 5
% 0.08/0.30  # Proof object clause conjectures      : 2
% 0.08/0.30  # Proof object formula conjectures     : 3
% 0.08/0.30  # Proof object initial clauses used    : 6
% 0.08/0.30  # Proof object initial formulas used   : 6
% 0.08/0.30  # Proof object generating inferences   : 3
% 0.08/0.30  # Proof object simplifying inferences  : 6
% 0.08/0.30  # Training examples: 0 positive, 0 negative
% 0.08/0.30  # Parsed axioms                        : 6
% 0.08/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.30  # Initial clauses                      : 9
% 0.08/0.30  # Removed in clause preprocessing      : 0
% 0.08/0.30  # Initial clauses in saturation        : 9
% 0.08/0.30  # Processed clauses                    : 23
% 0.08/0.30  # ...of these trivial                  : 0
% 0.08/0.30  # ...subsumed                          : 0
% 0.08/0.30  # ...remaining for further processing  : 23
% 0.08/0.30  # Other redundant clauses eliminated   : 0
% 0.08/0.30  # Clauses deleted for lack of memory   : 0
% 0.08/0.30  # Backward-subsumed                    : 0
% 0.08/0.30  # Backward-rewritten                   : 2
% 0.08/0.30  # Generated clauses                    : 5
% 0.08/0.30  # ...of the previous two non-trivial   : 5
% 0.08/0.30  # Contextual simplify-reflections      : 0
% 0.08/0.30  # Paramodulations                      : 3
% 0.08/0.30  # Factorizations                       : 0
% 0.08/0.30  # Equation resolutions                 : 2
% 0.08/0.30  # Propositional unsat checks           : 0
% 0.08/0.30  #    Propositional check models        : 0
% 0.08/0.30  #    Propositional check unsatisfiable : 0
% 0.08/0.30  #    Propositional clauses             : 0
% 0.08/0.30  #    Propositional clauses after purity: 0
% 0.08/0.30  #    Propositional unsat core size     : 0
% 0.08/0.30  #    Propositional preprocessing time  : 0.000
% 0.08/0.30  #    Propositional encoding time       : 0.000
% 0.08/0.30  #    Propositional solver time         : 0.000
% 0.08/0.30  #    Success case prop preproc time    : 0.000
% 0.08/0.30  #    Success case prop encoding time   : 0.000
% 0.08/0.30  #    Success case prop solver time     : 0.000
% 0.08/0.30  # Current number of processed clauses  : 12
% 0.08/0.30  #    Positive orientable unit clauses  : 8
% 0.08/0.30  #    Positive unorientable unit clauses: 0
% 0.08/0.30  #    Negative unit clauses             : 0
% 0.08/0.30  #    Non-unit-clauses                  : 4
% 0.08/0.30  # Current number of unprocessed clauses: 0
% 0.08/0.30  # ...number of literals in the above   : 0
% 0.08/0.30  # Current number of archived formulas  : 0
% 0.08/0.30  # Current number of archived clauses   : 11
% 0.08/0.30  # Clause-clause subsumption calls (NU) : 4
% 0.08/0.30  # Rec. Clause-clause subsumption calls : 4
% 0.08/0.30  # Non-unit clause-clause subsumptions  : 0
% 0.08/0.30  # Unit Clause-clause subsumption calls : 0
% 0.08/0.30  # Rewrite failures with RHS unbound    : 0
% 0.08/0.30  # BW rewrite match attempts            : 2
% 0.08/0.30  # BW rewrite match successes           : 2
% 0.08/0.30  # Condensation attempts                : 0
% 0.08/0.30  # Condensation successes               : 0
% 0.08/0.30  # Termbank termtop insertions          : 447
% 0.08/0.30  
% 0.08/0.30  # -------------------------------------------------
% 0.08/0.30  # User time                : 0.026 s
% 0.08/0.30  # System time              : 0.003 s
% 0.08/0.30  # Total time               : 0.029 s
% 0.08/0.30  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:50:16 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   44 (  50 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(t137_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(c_0_5,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | r1_tarski(k2_relat_1(k8_relat_1(X6,X7)),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t137_relat_1])).

fof(c_0_8,plain,(
    ! [X8] :
      ( ( k1_relat_1(X8) != k1_xboole_0
        | X8 = k1_xboole_0
        | ~ v1_relat_1(X8) )
      & ( k2_relat_1(X8) != k1_xboole_0
        | X8 = k1_xboole_0
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k8_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & k8_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_relat_1(k8_relat_1(k1_xboole_0,X1)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k8_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k8_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n004.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 12:33:38 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.34  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.12/0.34  # and selection function SelectCQIPrecWNTNp.
% 0.12/0.34  #
% 0.12/0.34  # Preprocessing time       : 0.027 s
% 0.12/0.34  # Presaturation interreduction done
% 0.12/0.34  
% 0.12/0.34  # Proof found!
% 0.12/0.34  # SZS status Theorem
% 0.12/0.34  # SZS output start CNFRefutation
% 0.12/0.34  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.12/0.34  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.12/0.34  fof(t137_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_relat_1)).
% 0.12/0.34  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.12/0.34  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.12/0.34  fof(c_0_5, plain, ![X3]:(~r1_tarski(X3,k1_xboole_0)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.12/0.34  fof(c_0_6, plain, ![X6, X7]:(~v1_relat_1(X7)|r1_tarski(k2_relat_1(k8_relat_1(X6,X7)),X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.12/0.34  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t137_relat_1])).
% 0.12/0.34  fof(c_0_8, plain, ![X8]:((k1_relat_1(X8)!=k1_xboole_0|X8=k1_xboole_0|~v1_relat_1(X8))&(k2_relat_1(X8)!=k1_xboole_0|X8=k1_xboole_0|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.12/0.34  cnf(c_0_9, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.34  cnf(c_0_10, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.34  fof(c_0_11, plain, ![X4, X5]:(~v1_relat_1(X5)|v1_relat_1(k8_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.12/0.34  fof(c_0_12, negated_conjecture, (v1_relat_1(esk1_0)&k8_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.34  cnf(c_0_13, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.34  cnf(c_0_14, plain, (k2_relat_1(k8_relat_1(k1_xboole_0,X1))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.34  cnf(c_0_15, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.34  cnf(c_0_16, negated_conjecture, (k8_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_17, plain, (k8_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.12/0.34  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_19, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), ['proof']).
% 0.12/0.34  # SZS output end CNFRefutation
% 0.12/0.34  # Proof object total steps             : 20
% 0.12/0.34  # Proof object clause steps            : 9
% 0.12/0.34  # Proof object formula steps           : 11
% 0.12/0.34  # Proof object conjectures             : 6
% 0.12/0.34  # Proof object clause conjectures      : 3
% 0.12/0.34  # Proof object formula conjectures     : 3
% 0.12/0.34  # Proof object initial clauses used    : 6
% 0.12/0.34  # Proof object initial formulas used   : 5
% 0.12/0.34  # Proof object generating inferences   : 3
% 0.12/0.34  # Proof object simplifying inferences  : 3
% 0.12/0.34  # Training examples: 0 positive, 0 negative
% 0.12/0.34  # Parsed axioms                        : 5
% 0.12/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.34  # Initial clauses                      : 7
% 0.12/0.34  # Removed in clause preprocessing      : 0
% 0.12/0.34  # Initial clauses in saturation        : 7
% 0.12/0.34  # Processed clauses                    : 17
% 0.12/0.34  # ...of these trivial                  : 0
% 0.12/0.34  # ...subsumed                          : 0
% 0.12/0.34  # ...remaining for further processing  : 17
% 0.12/0.34  # Other redundant clauses eliminated   : 0
% 0.12/0.34  # Clauses deleted for lack of memory   : 0
% 0.12/0.34  # Backward-subsumed                    : 0
% 0.12/0.34  # Backward-rewritten                   : 0
% 0.12/0.34  # Generated clauses                    : 9
% 0.12/0.34  # ...of the previous two non-trivial   : 7
% 0.12/0.34  # Contextual simplify-reflections      : 1
% 0.12/0.34  # Paramodulations                      : 9
% 0.12/0.34  # Factorizations                       : 0
% 0.12/0.34  # Equation resolutions                 : 0
% 0.12/0.34  # Propositional unsat checks           : 0
% 0.12/0.34  #    Propositional check models        : 0
% 0.12/0.34  #    Propositional check unsatisfiable : 0
% 0.12/0.34  #    Propositional clauses             : 0
% 0.12/0.34  #    Propositional clauses after purity: 0
% 0.12/0.34  #    Propositional unsat core size     : 0
% 0.12/0.34  #    Propositional preprocessing time  : 0.000
% 0.12/0.34  #    Propositional encoding time       : 0.000
% 0.12/0.34  #    Propositional solver time         : 0.000
% 0.12/0.34  #    Success case prop preproc time    : 0.000
% 0.12/0.34  #    Success case prop encoding time   : 0.000
% 0.12/0.34  #    Success case prop solver time     : 0.000
% 0.12/0.34  # Current number of processed clauses  : 10
% 0.12/0.34  #    Positive orientable unit clauses  : 1
% 0.12/0.34  #    Positive unorientable unit clauses: 0
% 0.12/0.34  #    Negative unit clauses             : 1
% 0.12/0.34  #    Non-unit-clauses                  : 8
% 0.12/0.34  # Current number of unprocessed clauses: 2
% 0.12/0.34  # ...number of literals in the above   : 3
% 0.12/0.34  # Current number of archived formulas  : 0
% 0.12/0.34  # Current number of archived clauses   : 7
% 0.12/0.34  # Clause-clause subsumption calls (NU) : 4
% 0.12/0.34  # Rec. Clause-clause subsumption calls : 4
% 0.12/0.34  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.34  # Unit Clause-clause subsumption calls : 0
% 0.12/0.34  # Rewrite failures with RHS unbound    : 0
% 0.12/0.34  # BW rewrite match attempts            : 0
% 0.12/0.34  # BW rewrite match successes           : 0
% 0.12/0.34  # Condensation attempts                : 0
% 0.12/0.34  # Condensation successes               : 0
% 0.12/0.34  # Termbank termtop insertions          : 512
% 0.12/0.34  
% 0.12/0.34  # -------------------------------------------------
% 0.12/0.34  # User time                : 0.028 s
% 0.12/0.34  # System time              : 0.003 s
% 0.12/0.34  # Total time               : 0.031 s
% 0.12/0.34  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
